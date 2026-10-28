import ThetLogos.PlaneCrossingBeta4
import ThetLogos.RepOrthogonality

/-
# PW-2: the telescoping evaluation of `quadReMoment`, and the sign of Φ

Brick PW-2 of the projector scoping
(`scoping-pw-projector-2026-10-27.md` §2), on top of PW-1
(`RepOrthogonality`: entry orthogonality of `repMatrix` at
irreducible `ρ`, the evaluated pair twirl, the evaluated
conjugation twirl). Target: the sign of
`Φ(u, u') := ∑ C ∈ primitiveQuads, (quadReMoment C u u' − e₁⁴)`,
to which `kappa4dep_sign_reduction` (Beta4) reduces the sign of
the β⁴ dependent coefficient `κ₄^dep`.

## HONESTY LEDGER — read this before citing anything from this file

**(i) NO CLAIM; dials 0/4.** Parts of the official Clay
Yang–Mills statement closed by this module: **0**. This is
finite-volume lattice algebra and compact-group representation
algebra. No limit is taken or asserted; nothing here is a
statement about `𝒜 ⪰ 0` in the large, and nothing about orders
β⁵ and beyond.

**(ii) Verdict of this brick: PARTIAL, by the pre-registered kill
K-PW-2.** The telescoping evaluation of `quadReMoment` is carried
as far as the owned orthogonality reaches, and it stops at a
named component (item (iv)). What is FULL here:

* §1, the **contraction formula, stage one** (general `(G, ρ)`,
  no irreducibility): `quadReMoment` is exactly `2⁻⁴` times the
  real part of the sum, over the subsets `t ⊆ C`, of the complex
  character moments `quadCharMoment C t` — the columns in `t`
  taken plain, the columns in `C ∖ t` taken conjugated. Expanding
  each character as a trace of `repMatrix` of the column word
  turns each complex moment into a tensor-network contraction
  over the site-sharing graph of `C`, with frozen-link entries
  outside and one Haar integral per site inside.
* §2, the **telescoping step itself**, as standalone integral
  identities at irreducible `ρ`: the mixed-pair contraction
  `∫ tr(P ρ(g)) tr(Q · star ρ(g)) = d⁻¹ tr(P Q)`, its four-matrix
  sewing form, and the character sewing
  `∫ χ(a g b) χ(c g⁻¹ d) dg = d⁻¹ χ(b a d c)`. These are what
  PW-1's entry orthogonality buys at every site whose incident
  factors are one plain and one conjugated entry.
* §3, **one family evaluated completely**: the digon pair — a
  column and its reverse over the same site pair, at diagonal
  links. Its local factor is the iterated integral
  `∫∫ χ(A x B⁻¹ x⁻¹) χ(B x A⁻¹ x⁻¹) = d⁻² · χ(x²) · star χ(x²)`,
  a single square, exhibited: `d⁻² |χ(x²)|² ≥ 0`. The inner
  integral is the character sewing; the outer is PW-1's
  evaluated conjugation twirl.

**(iii) Scope flag (pre-registered K-PW-1b, inherited from
PW-1).** Every statement in §2–§3 is proved for **irreducible**
`ρ` only. §1 and §4 need no irreducibility. If the sign of
`κ₄^dep` is ever stated at reducible `ρ`, it must carry
irreducibility as a hypothesis; this module does not paper over
that.

**(iv) The surviving term (K-PW-2, named exactly).** The complex
moments of §1 whose site contractions pass through a
**same-orientation pair** — two plain entries `ρ(α s)`, or two
conjugated entries, at one site — or through a site carrying
**three or more** incident factors, are **not** evaluated here.
Their site integrals are entries of the `ρ ⊗ ρ` (resp.
`ρ̄ ⊗ ρ̄`) twirl, or of higher tensor twirls: projectors onto
invariant subspaces that PW-1 did not evaluate (PW-1 evaluated
the mixed twirl `ρ ⊗ ρ̄` only; the `ρ ⊗ ρ` evaluation is a
different Schur problem, needing the invariant bilinear form of
`ρ`). §4 states `Φ` *as* the sum of §1's complex moments minus
`e₁⁴` (`phiFunctional_eq`) and the exact identity
`κ₄^dep(u, u) = (d : ℝ)⁻⁴ · Φ(u)`
(`kappa4dep_diag_eq_phi`): the sign of `κ₄^dep` on the diagonal
is the sign of that named, unevaluated part. Seat totals (probe
module `PlaneCrossingKappa4Probe`, N = 2): at both probed seats
the total diagonal is nonnegative with margin exactly zero, so
the surviving term is seat-consistent with `Φ ≥ 0` and no
certified negative direction exists at any owned seat — the
K-K4G-1 refutation pathway does not fire. The sign in general
remains **open**, at exactly the component named here.

This module is NOT in the root import list of the library (the
corpus pattern for recent bricks); it is verified by a targeted
build.
-/

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix

section Telescope

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]
  (μG : Measure G) [IsProbabilityMeasure μG]
  [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant] [μG.IsInvInvariant]

/-! ## §1. The contraction formula, stage one: the subset expansion

For a finite set of columns `C` and a subset `t ⊆ C`, the complex
character moment takes the columns of `t` plain and the columns
of `C ∖ t` conjugated. `Re z = (z + z̄)/2`, expanded over the
product, writes `quadReMoment` as `2^(-|C|)` times the real part
of the sum of these moments. -/

/-- The **complex character moment** of a column set `C` with
sign pattern `t`: `∫ ∏_{P ∈ t} χ(W_P) · ∏_{P ∈ C ∖ t} χ(W_P)̄`,
the stratum integral of the plain characters over `t` times the
conjugated characters over `C ∖ t`. -/
noncomputable def quadCharMoment (C t : Finset (LayerColumn N))
    (u u' : LayerLink N → G) : ℂ :=
  ∫ α, (∏ P ∈ t, charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α))
      * (∏ P ∈ C \ t, star (charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α)))
    ∂(Measure.pi fun _ : LayerSite N => μG)

private theorem measurable_charFn_colWord
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (P : LayerColumn N) :
    Measurable (fun α : LayerSite N → G =>
      charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α)) :=
  (measurable_charFn ρ hρcont).comp (measurable_colWord u u' P.1 P.2.1 P.2.2)

private theorem integrable_quadCharIntegrand
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (C t : Finset (LayerColumn N)) (u u' : LayerLink N → G) :
    Integrable (fun α : LayerSite N → G =>
      (∏ P ∈ t, charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α))
        * (∏ P ∈ C \ t, star (charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α))))
      (Measure.pi fun _ : LayerSite N => μG) := by
  have hmeas1 : Measurable (fun α : LayerSite N → G =>
      ∏ P ∈ t, charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α)) :=
    Finset.measurable_prod _ fun P _ => measurable_charFn_colWord ρ hρcont u u' P
  have hmeas2 : Measurable (fun α : LayerSite N → G =>
      ∏ P ∈ C \ t, star (charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α))) :=
    Finset.measurable_prod _ fun P _ =>
      continuous_star.measurable.comp (measurable_charFn_colWord ρ hρcont u u' P)
  refine Integrable.of_bound (hmeas1.mul hmeas2).aestronglyMeasurable
    ((d : ℝ) ^ (t.card + (C \ t).card)) (Filter.Eventually.of_forall fun α => ?_)
  calc ‖(∏ P ∈ t, charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α))
        * (∏ P ∈ C \ t, star (charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α)))‖
      = ‖∏ P ∈ t, charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α)‖
        * ‖∏ P ∈ C \ t, star (charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α))‖ :=
        norm_mul _ _
    _ ≤ (∏ P ∈ t, ‖charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α)‖)
        * (∏ P ∈ C \ t, ‖star (charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α))‖) :=
        mul_le_mul (Finset.norm_prod_le t _) (Finset.norm_prod_le (C \ t) _)
          (norm_nonneg _)
          (Finset.prod_nonneg fun P _ => norm_nonneg _)
    _ ≤ (∏ _P ∈ t, (d : ℝ)) * (∏ _P ∈ C \ t, (d : ℝ)) :=
        mul_le_mul
          (Finset.prod_le_prod₀ (fun P _ => norm_nonneg _)
            (fun P _ => norm_charFn_le ρ _))
          (Finset.prod_le_prod₀ (fun P _ => by rw [norm_star]; exact norm_nonneg _)
            (fun P _ => by rw [norm_star]; exact norm_charFn_le ρ _))
          (Finset.prod_nonneg fun _ _ => by rw [norm_star]; exact norm_nonneg _)
          (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg d)
    _ = (d : ℝ) ^ (t.card + (C \ t).card) := by
        rw [Finset.prod_const, Finset.prod_const, ← pow_add]

/-- One real character value as a complex number is the average
of the character and its conjugate. -/
private theorem ofReal_colRe_eq (u u' : LayerLink N → G) (P : LayerColumn N)
    (α : LayerSite N → G) :
    ((colRe ρ u u' P α : ℝ) : ℂ)
      = (charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α)
        + star (charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α))) * (2 : ℂ)⁻¹ := by
  have havg : ∀ z : ℂ, ((z.re : ℂ)) = (z + star z) * (2 : ℂ)⁻¹ := by
    intro z
    rw [show ((z.re : ℂ)) = (z + (starRingEnd ℂ) z) / 2 from
        RCLike.re_eq_add_conj z, div_eq_mul_inv, starRingEnd_apply]
  calc ((colRe ρ u u' P α : ℝ) : ℂ)
      = ((charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α)).re : ℂ) := rfl
    _ = (charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α)
          + star (charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α))) * (2 : ℂ)⁻¹ :=
        havg _

/-- The pointwise subset expansion of a product of real
characters, as a complex identity. -/
private theorem prod_colRe_eq (C : Finset (LayerColumn N))
    (u u' : LayerLink N → G) (α : LayerSite N → G) :
    ((∏ P ∈ C, colRe ρ u u' P α : ℝ) : ℂ)
      = ((2 : ℂ)⁻¹) ^ C.card * ∑ t ∈ C.powerset,
          (∏ P ∈ t, charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α))
            * (∏ P ∈ C \ t, star (charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α))) := by
  rw [Complex.ofReal_prod]
  have hfac : ∀ P ∈ C, ((colRe ρ u u' P α : ℝ) : ℂ)
      = (charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α)
        + star (charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α))) * (2 : ℂ)⁻¹ :=
    fun P _ => ofReal_colRe_eq ρ u u' P α
  have hprod : (∏ P ∈ C, ((colRe ρ u u' P α : ℝ) : ℂ))
      = ∏ P ∈ C, ((charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α)
        + star (charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α))) * (2 : ℂ)⁻¹) :=
    Finset.prod_congr rfl hfac
  rw [hprod, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_add]
  exact mul_comm _ _

/-- **The contraction formula, stage one** (general `(G, ρ)`; no
irreducibility used): `quadReMoment` is `2^(-|C|)` times the real
part of the sum of the complex character moments over all sign
patterns `t ⊆ C`. -/
theorem quadReMoment_eq_sum_quadCharMoment
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (C : Finset (LayerColumn N)) (u u' : LayerLink N → G) :
    quadReMoment ρ μG C u u'
      = ((2 : ℝ)⁻¹) ^ C.card
        * (∑ t ∈ C.powerset, quadCharMoment ρ μG C t u u').re := by
  have hcast : ((quadReMoment ρ μG C u u' : ℝ) : ℂ)
      = ((2 : ℂ)⁻¹) ^ C.card
        * ∑ t ∈ C.powerset, quadCharMoment ρ μG C t u u' := by
    have h1 : ((quadReMoment ρ μG C u u' : ℝ) : ℂ)
        = ∫ α, ((∏ P ∈ C, colRe ρ u u' P α : ℝ) : ℂ)
            ∂(Measure.pi fun _ : LayerSite N => μG) := by
      have hofr : (∫ α, ((∏ P ∈ C, colRe ρ u u' P α : ℝ) : ℂ)
            ∂(Measure.pi fun _ : LayerSite N => μG))
          = ((∫ α, ∏ P ∈ C, colRe ρ u u' P α
              ∂(Measure.pi fun _ : LayerSite N => μG) : ℝ) : ℂ) :=
        integral_ofReal
      rw [hofr]
      rfl
    rw [h1]
    have h2 : ∫ α, ((∏ P ∈ C, colRe ρ u u' P α : ℝ) : ℂ)
          ∂(Measure.pi fun _ : LayerSite N => μG)
        = ∫ α, ((2 : ℂ)⁻¹) ^ C.card * ∑ t ∈ C.powerset,
            (∏ P ∈ t, charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α))
              * (∏ P ∈ C \ t, star (charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α)))
          ∂(Measure.pi fun _ : LayerSite N => μG) :=
      integral_congr_ae (Filter.Eventually.of_forall fun α =>
        prod_colRe_eq ρ C u u' α)
    rw [h2]
    calc ∫ α, ((2 : ℂ)⁻¹) ^ C.card * ∑ t ∈ C.powerset,
            (∏ P ∈ t, charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α))
              * (∏ P ∈ C \ t, star (charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α)))
          ∂(Measure.pi fun _ : LayerSite N => μG)
        = ((2 : ℂ)⁻¹) ^ C.card * ∫ α, ∑ t ∈ C.powerset,
            (∏ P ∈ t, charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α))
              * (∏ P ∈ C \ t, star (charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α)))
          ∂(Measure.pi fun _ : LayerSite N => μG) :=
          integral_const_mul _ _
      _ = ((2 : ℂ)⁻¹) ^ C.card
            * ∑ t ∈ C.powerset, ∫ α,
              (∏ P ∈ t, charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α))
                * (∏ P ∈ C \ t, star (charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α)))
              ∂(Measure.pi fun _ : LayerSite N => μG) := by
          congr 1
          exact MeasureTheory.integral_finsetSum C.powerset
            (fun t _ => integrable_quadCharIntegrand ρ μG hρcont C t u u')
      _ = ((2 : ℂ)⁻¹) ^ C.card
            * ∑ t ∈ C.powerset, quadCharMoment ρ μG C t u u' := rfl
  have hre := congrArg Complex.re hcast
  rw [Complex.ofReal_re] at hre
  have hsc : (((2 : ℂ)⁻¹) ^ C.card
      * ∑ t ∈ C.powerset, quadCharMoment ρ μG C t u u').re
      = ((2 : ℝ)⁻¹) ^ C.card
        * (∑ t ∈ C.powerset, quadCharMoment ρ μG C t u u').re := by
    have hc : ((2 : ℂ)⁻¹) ^ C.card = ((((2 : ℝ)⁻¹) ^ C.card : ℝ) : ℂ) := by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_cast, ← Complex.ofReal_inv,
        ← Complex.ofReal_pow]
    rw [hc]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      zero_mul, sub_zero]
  rw [hsc] at hre
  exact hre

/-- **The contraction formula at a primitive quad**: the stage-one
expansion with the pattern count `2⁴`. The further site-by-site
evaluation of the moments on the right is exactly where the
telescoping of §2–§3 applies — and where, at same-orientation or
multiply-incident sites, it stops (the surviving term of the
honesty ledger). -/
theorem quadReMoment_primitive_eq
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    {C : Finset (LayerColumn N)} (hC : IsPrimitiveQuad C)
    (u u' : LayerLink N → G) :
    quadReMoment ρ μG C u u'
      = ((2 : ℝ)⁻¹) ^ 4
        * (∑ t ∈ C.powerset, quadCharMoment ρ μG C t u u').re := by
  rw [quadReMoment_eq_sum_quadCharMoment ρ μG hρcont C u u', hC.1]

/-! ## §2. The sewing step (PW-1-powered)

At a site whose incident factors are exactly one `repMatrix` entry
and one `star` entry — a *mixed pair* — the Haar integral is PW-1's
orthogonality.  In trace form it sews two loops into one; in
character form it is the Peter–Weyl sewing of two words along an
inverse letter. -/

/-- Integrability of a mixed-pair entry product. -/
theorem integrable_repMatrix_entry_mul_star
    (hρcont : Continuous fun g : G => repMatrix ρ g) (i j k l : Fin d) :
    Integrable (fun g => repMatrix ρ g i j * star (repMatrix ρ g k l))
      μG := by
  obtain ⟨hMmul, hMone, hMinv, hMcont⟩ := repMatrix_isOrientationMat ρ hρcont
  obtain ⟨hNmul, hNone, hNinv, hNcont⟩ := repMatConj_isOrientationMat ρ hρcont
  have hInt : Integrable (fun g => repMatrix ρ g i j * repMatConj ρ g k l)
      μG :=
    matFn_integrable_entry_mul μG _ _ hMmul hMone hMinv hMcont
      hNmul hNone hNinv hNcont i j k l
  refine hInt.congr (Filter.Eventually.of_forall fun g => ?_)
  show repMatrix ρ g i j * repMatConj ρ g k l
    = repMatrix ρ g i j * star (repMatrix ρ g k l)
  rw [show repMatConj ρ g k l = star (repMatrix ρ g k l) from
    orientConj_apply _ _ _ _]

section Sewing

variable (P Q : Matrix (Fin d) (Fin d) ℂ)

/-- Integrability, three inner sums of the sewing expansion. -/
theorem integrable_trace_mul_trace_star_s3
    (hρcont : Continuous fun g : G => repMatrix ρ g) (i : Fin d) :
    Integrable (fun g => ∑ j, ∑ k, ∑ l, (P i j * Q k l)
      * (repMatrix ρ g j i * star (repMatrix ρ g k l))) μG :=
  MeasureTheory.integrable_finsetSum Finset.univ fun j _ =>
    MeasureTheory.integrable_finsetSum Finset.univ fun k _ =>
      MeasureTheory.integrable_finsetSum Finset.univ fun l _ =>
        (integrable_repMatrix_entry_mul_star ρ μG hρcont j i k l).const_mul _

/-- Integrability, two inner sums of the sewing expansion. -/
theorem integrable_trace_mul_trace_star_s2
    (hρcont : Continuous fun g : G => repMatrix ρ g) (i j : Fin d) :
    Integrable (fun g => ∑ k, ∑ l, (P i j * Q k l)
      * (repMatrix ρ g j i * star (repMatrix ρ g k l))) μG :=
  MeasureTheory.integrable_finsetSum Finset.univ fun k _ =>
    MeasureTheory.integrable_finsetSum Finset.univ fun l _ =>
      (integrable_repMatrix_entry_mul_star ρ μG hρcont j i k l).const_mul _

/-- Integrability, one inner sum of the sewing expansion. -/
theorem integrable_trace_mul_trace_star_s1
    (hρcont : Continuous fun g : G => repMatrix ρ g) (i j k : Fin d) :
    Integrable (fun g => ∑ l, (P i j * Q k l)
      * (repMatrix ρ g j i * star (repMatrix ρ g k l))) μG :=
  MeasureTheory.integrable_finsetSum Finset.univ fun l _ =>
    (integrable_repMatrix_entry_mul_star ρ μG hρcont j i k l).const_mul _

/-- The sewing expansion collapses: at fixed first index pair
`(i, j)`, the double sum over the second factor's indices picks out
exactly `(P i j * Q j i) * (d)⁻¹`. -/
theorem sewing_collapse (i j : Fin d) :
    (∑ k, ∑ l, (P i j * Q k l)
        * (if j = k ∧ i = l then (d : ℂ)⁻¹ else 0))
      = (P i j * Q j i) * (d : ℂ)⁻¹ := by
  have step1 : (∑ k, ∑ l, (P i j * Q k l)
        * (if j = k ∧ i = l then (d : ℂ)⁻¹ else 0))
      = ∑ l, (P i j * Q j l) * (if j = j ∧ i = l then (d : ℂ)⁻¹ else 0) := by
    refine Finset.sum_eq_single j (fun k _ hk => ?_)
      (fun hj => absurd (Finset.mem_univ j) hj)
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [if_neg (fun h => hk h.1.symm)]
    exact mul_zero _
  have step1' : (∑ l, (P i j * Q j l)
        * (if j = j ∧ i = l then (d : ℂ)⁻¹ else 0))
      = ∑ l, (P i j * Q j l) * (if i = l then (d : ℂ)⁻¹ else 0) :=
    Finset.sum_congr rfl fun l _ => by simp
  have step2 : (∑ l, (P i j * Q j l) * (if i = l then (d : ℂ)⁻¹ else 0))
      = ∑ l, (if i = l then (P i j * Q j l) * (d : ℂ)⁻¹ else 0) :=
    Finset.sum_congr rfl fun l _ => by rw [mul_ite, mul_zero]
  rw [step1, step1', step2, Finset.sum_ite_eq Finset.univ i
    (fun l => (P i j * Q j l) * (d : ℂ)⁻¹), if_pos (Finset.mem_univ i)]

/-- **The sewing identity (trace form).**  Integrating the product
of two traces against a mixed pair collapses them to a single
trace, with the `1 / d` of PW-1 orthogonality. -/
theorem integral_trace_mul_trace_star
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hρirr : RepIrreducible ρ) :
    ∫ g, Matrix.trace (P * repMatrix ρ g)
        * Matrix.trace (Q * star (repMatrix ρ g)) ∂μG
      = (d : ℂ)⁻¹ * Matrix.trace (P * Q) := by
  have hexp : ∀ g : G, Matrix.trace (P * repMatrix ρ g)
        * Matrix.trace (Q * star (repMatrix ρ g))
      = ∑ i, ∑ j, ∑ k, ∑ l, (P i j * Q k l)
          * (repMatrix ρ g j i * star (repMatrix ρ g k l)) := by
    intro g
    have e1 : Matrix.trace (P * repMatrix ρ g)
        = ∑ i, ∑ j, P i j * repMatrix ρ g j i := by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    have e2 : Matrix.trace (Q * star (repMatrix ρ g))
        = ∑ k, ∑ l, Q k l * star (repMatrix ρ g k l) := by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply,
        Matrix.star_apply]
    rw [e1, e2, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  have hterm : ∀ i j k l : Fin d,
      (∫ g, (P i j * Q k l)
          * (repMatrix ρ g j i * star (repMatrix ρ g k l)) ∂μG)
        = (P i j * Q k l) * (if j = k ∧ i = l then (d : ℂ)⁻¹ else 0) := by
    intro i j k l
    rw [integral_const_mul,
      integral_repMatrix_mul_star_repMatrix μG ρ hρcont hρirr j i k l]
  have hswap : (∫ g, ∑ i, ∑ j, ∑ k, ∑ l, (P i j * Q k l)
          * (repMatrix ρ g j i * star (repMatrix ρ g k l)) ∂μG)
      = ∑ i, ∑ j, ∑ k, ∑ l, ∫ g, (P i j * Q k l)
          * (repMatrix ρ g j i * star (repMatrix ρ g k l)) ∂μG :=
    (MeasureTheory.integral_finsetSum Finset.univ
      (fun i _ => integrable_trace_mul_trace_star_s3 ρ μG P Q hρcont i)).trans
      (Finset.sum_congr rfl fun i _ =>
        (MeasureTheory.integral_finsetSum Finset.univ
          (fun j _ => integrable_trace_mul_trace_star_s2 ρ μG P Q hρcont
            i j)).trans
          (Finset.sum_congr rfl fun j _ =>
            (MeasureTheory.integral_finsetSum Finset.univ
              (fun k _ => integrable_trace_mul_trace_star_s1 ρ μG P Q
                hρcont i j k)).trans
              (Finset.sum_congr rfl fun k _ =>
                MeasureTheory.integral_finsetSum Finset.univ
                  (fun l _ => (integrable_repMatrix_entry_mul_star ρ μG
                    hρcont j i k l).const_mul _))))
  rw [integral_congr_ae (Filter.Eventually.of_forall hexp), hswap]
  have hsum : (∑ i, ∑ j, ∑ k, ∑ l, ∫ g, (P i j * Q k l)
          * (repMatrix ρ g j i * star (repMatrix ρ g k l)) ∂μG)
      = ∑ i, ∑ j, (P i j * Q j i) * (d : ℂ)⁻¹ :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      (Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ =>
        hterm i j k l).trans (sewing_collapse P Q i j)
  rw [hsum, show Matrix.trace (P * Q) = ∑ i, ∑ j, P i j * Q j i from by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply], Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

end Sewing

/-- **The sewing identity (four-matrix form).**  Frozen links on
both sides of the two traces: the integral sews the loop
`B A D C`. -/
theorem integral_trace_mul_trace_star_apply
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hρirr : RepIrreducible ρ)
    (A B C D : Matrix (Fin d) (Fin d) ℂ) :
    ∫ g, Matrix.trace (A * repMatrix ρ g * B)
        * Matrix.trace (C * star (repMatrix ρ g) * D) ∂μG
      = (d : ℂ)⁻¹ * Matrix.trace (B * A * D * C) := by
  have e1' : ∀ g : G, Matrix.trace (A * repMatrix ρ g * B)
      = Matrix.trace ((B * A) * repMatrix ρ g) := by
    intro g
    calc Matrix.trace (A * repMatrix ρ g * B)
        = Matrix.trace (B * (A * repMatrix ρ g)) :=
          Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((B * A) * repMatrix ρ g) := by
          rw [Matrix.mul_assoc]
  have e2' : ∀ g : G, Matrix.trace (C * star (repMatrix ρ g) * D)
      = Matrix.trace ((D * C) * star (repMatrix ρ g)) := by
    intro g
    calc Matrix.trace (C * star (repMatrix ρ g) * D)
        = Matrix.trace (D * (C * star (repMatrix ρ g))) :=
          Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((D * C) * star (repMatrix ρ g)) := by
          rw [Matrix.mul_assoc]
  have e : ∀ g : G, Matrix.trace (A * repMatrix ρ g * B)
        * Matrix.trace (C * star (repMatrix ρ g) * D)
      = Matrix.trace ((B * A) * repMatrix ρ g)
          * Matrix.trace ((D * C) * star (repMatrix ρ g)) := by
    intro g
    rw [e1' g, e2' g]
  rw [integral_congr_ae (Filter.Eventually.of_forall e),
    integral_trace_mul_trace_star ρ μG (B * A) (D * C) hρcont hρirr,
    ← Matrix.mul_assoc (B * A) D C]

/-- **The sewing identity (character form).**  Two words sharing an
inverse letter sew into one word; the price is `1 / d`. -/
theorem integral_charFn_mul_charFn_inv
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hρirr : RepIrreducible ρ) (a b c d' : G) :
    ∫ g, charFn ρ (a * g * b) * charFn ρ (c * g⁻¹ * d') ∂μG
      = (d : ℂ)⁻¹ * charFn ρ (b * a * d' * c) := by
  have e : ∀ g : G, charFn ρ (a * g * b) * charFn ρ (c * g⁻¹ * d')
      = Matrix.trace (repMatrix ρ a * repMatrix ρ g * repMatrix ρ b)
        * Matrix.trace (repMatrix ρ c * star (repMatrix ρ g)
            * repMatrix ρ d') := by
    intro g
    have e1 : charFn ρ (a * g * b)
        = Matrix.trace (repMatrix ρ a * repMatrix ρ g * repMatrix ρ b) := by
      show Matrix.trace (repMatrix ρ (a * g * b)) = _
      rw [repMatrix_mul, repMatrix_mul]
    have e2 : charFn ρ (c * g⁻¹ * d')
        = Matrix.trace (repMatrix ρ c * star (repMatrix ρ g)
            * repMatrix ρ d') := by
      show Matrix.trace (repMatrix ρ (c * g⁻¹ * d')) = _
      rw [repMatrix_mul, repMatrix_mul, repMatrix_inv]
    rw [e1, e2]
  have hfin : repMatrix ρ b * repMatrix ρ a * repMatrix ρ d' * repMatrix ρ c
      = repMatrix ρ (b * a * d' * c) := by
    rw [← repMatrix_mul, ← repMatrix_mul, ← repMatrix_mul]
  calc ∫ g, charFn ρ (a * g * b) * charFn ρ (c * g⁻¹ * d') ∂μG
      = ∫ g, Matrix.trace (repMatrix ρ a * repMatrix ρ g * repMatrix ρ b)
          * Matrix.trace (repMatrix ρ c * star (repMatrix ρ g)
              * repMatrix ρ d') ∂μG :=
        integral_congr_ae (Filter.Eventually.of_forall e)
    _ = (d : ℂ)⁻¹ * Matrix.trace (repMatrix ρ b * repMatrix ρ a
          * repMatrix ρ d' * repMatrix ρ c) :=
        integral_trace_mul_trace_star_apply ρ μG hρcont hρirr _ _ _ _
    _ = (d : ℂ)⁻¹ * charFn ρ (b * a * d' * c) := by
        have htr : Matrix.trace (repMatrix ρ b * repMatrix ρ a
              * repMatrix ρ d' * repMatrix ρ c)
            = charFn ρ (b * a * d' * c) :=
          congrArg Matrix.trace hfin
        rw [htr]

/-! ## §3. One family closes completely: the digon pair

For a column `P` and its reverse over the same site pair, the two
shared variables form a single 2-cycle: both site integrals are
mixed pairs after the inversion substitution, the sewing of §2
applies, and the remaining conjugation average is the evaluated
twirl of PW-1.  The local factor is a single square. -/

/-- **The conjugation twirl in character form.**  Averaging the
commutator word `A y A⁻¹ y⁻¹` over `A` gives
`(d)⁻¹ · χ(y) · conj χ(y)` — a single square, since
`χ(y⁻¹) = conj χ(y)`. -/
theorem integral_charFn_conj_twirl
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hρirr : RepIrreducible ρ) (hd : 0 < d) (y : G) :
    ∫ A, charFn ρ (A * y * A⁻¹ * y⁻¹) ∂μG
      = (d : ℂ)⁻¹ * (charFn ρ y * star (charFn ρ y)) := by
  have hstarRE : star (charFn ρ y) = charFn ρ y⁻¹ := by
    rw [charFn_inv, starRingEnd_apply]
  have hpt : ∀ A : G, charFn ρ (A * y * A⁻¹ * y⁻¹)
      = Matrix.trace (repMatrix ρ y⁻¹
          * (repMatrix ρ A * repMatrix ρ y * star (repMatrix ρ A))) := by
    intro A
    show Matrix.trace (repMatrix ρ (A * y * A⁻¹ * y⁻¹)) = _
    rw [repMatrix_mul, repMatrix_mul, repMatrix_mul, repMatrix_inv,
      Matrix.trace_mul_comm
        (repMatrix ρ A * repMatrix ρ y * star (repMatrix ρ A))
        (repMatrix ρ y⁻¹)]
  have hIntEntry : ∀ i : Fin d, Integrable
      (fun A => (repMatrix ρ y⁻¹
        * (repMatrix ρ A * repMatrix ρ y * star (repMatrix ρ A))) i i)
      μG := by
    intro i
    have hsum : Integrable (fun A => ∑ j, (repMatrix ρ y⁻¹) i j
        * (repMatrix ρ A * repMatrix ρ y * star (repMatrix ρ A)) j i) μG :=
      MeasureTheory.integrable_finsetSum Finset.univ fun j _ =>
        (twirlEndo_entry_integrable μG ρ hρcont (repMatrix ρ y) j i).const_mul _
    refine hsum.congr (Filter.Eventually.of_forall fun A => ?_)
    show (repMatrix ρ y⁻¹
          * (repMatrix ρ A * repMatrix ρ y * star (repMatrix ρ A))) i i
        = ∑ j, (repMatrix ρ y⁻¹) i j
            * (repMatrix ρ A * repMatrix ρ y * star (repMatrix ρ A)) j i
    rw [Matrix.mul_apply]
  have hentry : ∀ i : Fin d,
      (∫ A, (repMatrix ρ y⁻¹
          * (repMatrix ρ A * repMatrix ρ y * star (repMatrix ρ A))) i i ∂μG)
        = (repMatrix ρ y⁻¹ * twirlEndo μG (repMatrix ρ) (repMatrix ρ y)) i i := by
    intro i
    have hpt2 : ∀ A : G, (repMatrix ρ y⁻¹
          * (repMatrix ρ A * repMatrix ρ y * star (repMatrix ρ A))) i i
        = ∑ j, (repMatrix ρ y⁻¹) i j
            * (repMatrix ρ A * repMatrix ρ y * star (repMatrix ρ A)) j i :=
      fun A => by rw [Matrix.mul_apply]
    have hRHS : (repMatrix ρ y⁻¹ * twirlEndo μG (repMatrix ρ) (repMatrix ρ y)) i i
        = ∑ j, (repMatrix ρ y⁻¹) i j
            * (twirlEndo μG (repMatrix ρ) (repMatrix ρ y)) j i := by
      rw [Matrix.mul_apply]
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt2),
      MeasureTheory.integral_finsetSum Finset.univ
        (fun j _ => (twirlEndo_entry_integrable μG ρ hρcont
          (repMatrix ρ y) j i).const_mul _), hRHS]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, twirlEndo_apply]
  calc ∫ A, charFn ρ (A * y * A⁻¹ * y⁻¹) ∂μG
      = ∫ A, Matrix.trace (repMatrix ρ y⁻¹
          * (repMatrix ρ A * repMatrix ρ y * star (repMatrix ρ A))) ∂μG :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = ∑ i, ∫ A, (repMatrix ρ y⁻¹
          * (repMatrix ρ A * repMatrix ρ y * star (repMatrix ρ A))) i i ∂μG := by
        have htr : (∫ A, Matrix.trace (repMatrix ρ y⁻¹
              * (repMatrix ρ A * repMatrix ρ y * star (repMatrix ρ A))) ∂μG)
            = ∫ A, ∑ i, (repMatrix ρ y⁻¹
              * (repMatrix ρ A * repMatrix ρ y * star (repMatrix ρ A))) i i ∂μG :=
          integral_congr_ae (Filter.Eventually.of_forall fun A => by
            simp only [Matrix.trace, Matrix.diag])
        rw [htr]
        exact MeasureTheory.integral_finsetSum Finset.univ
          (fun i _ => hIntEntry i)
    _ = ∑ i, (repMatrix ρ y⁻¹ * twirlEndo μG (repMatrix ρ) (repMatrix ρ y)) i i :=
        Finset.sum_congr rfl fun i _ => hentry i
    _ = Matrix.trace (repMatrix ρ y⁻¹
          * twirlEndo μG (repMatrix ρ) (repMatrix ρ y)) := by
        simp only [Matrix.trace, Matrix.diag]
    _ = Matrix.trace (repMatrix ρ y⁻¹
          * (((d : ℂ)⁻¹ * (repMatrix ρ y).trace)
            • (1 : Matrix (Fin d) (Fin d) ℂ))) := by
        rw [twirlEndo_repMatrix_eq μG ρ hd hρirr hρcont]
    _ = (d : ℂ)⁻¹ * (charFn ρ y * star (charFn ρ y)) := by
        have hsm : repMatrix ρ y⁻¹
              * (((d : ℂ)⁻¹ * (repMatrix ρ y).trace)
                • (1 : Matrix (Fin d) (Fin d) ℂ))
            = ((d : ℂ)⁻¹ * (repMatrix ρ y).trace) • repMatrix ρ y⁻¹ := by
          rw [Matrix.mul_smul, Matrix.mul_one]
        rw [hsm, Matrix.trace_smul, hstarRE]
        show ((d : ℂ)⁻¹ * (repMatrix ρ y).trace) * (repMatrix ρ y⁻¹).trace
            = (d : ℂ)⁻¹ * ((repMatrix ρ y).trace * (repMatrix ρ y⁻¹).trace)
        exact mul_assoc _ _ _

/-- **The digon-pair local factor.**  For a column and its reverse
over the same site pair, with diagonal frozen link `x` (the column's
link at `u' = u`), the two-variable local factor of the constant
sign pattern is `(d)⁻² · χ(x²) · conj χ(x²)` — one square, exhibited.
The inner integral is the sewing of §2 after the inversion
substitution; the outer is the conjugation twirl above. -/
theorem digon_pair_factor
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hρirr : RepIrreducible ρ) (hd : 0 < d) (x : G) :
    ∫ A, ∫ B, charFn ρ (A * x * B⁻¹ * x⁻¹) * charFn ρ (B * x * A⁻¹ * x⁻¹)
        ∂μG ∂μG
      = ((d : ℂ)⁻¹) ^ 2 * (charFn ρ (x * x) * star (charFn ρ (x * x))) := by
  have hinner : ∀ A : G, (∫ B, charFn ρ (A * x * B⁻¹ * x⁻¹)
        * charFn ρ (B * x * A⁻¹ * x⁻¹) ∂μG)
      = (d : ℂ)⁻¹ * charFn ρ (A * (x * x) * A⁻¹ * (x * x)⁻¹) := by
    intro A
    have hsub : (∫ B, charFn ρ (A * x * B⁻¹ * x⁻¹)
          * charFn ρ (B * x * A⁻¹ * x⁻¹) ∂μG)
        = ∫ B, charFn ρ (A * x * B * x⁻¹) * charFn ρ (B⁻¹ * x * A⁻¹ * x⁻¹)
            ∂μG := by
      have h0 := (integral_inv_eq_self (fun B => charFn ρ (A * x * B⁻¹ * x⁻¹)
        * charFn ρ (B * x * A⁻¹ * x⁻¹)) μG).symm
      refine h0.trans (integral_congr_ae (Filter.Eventually.of_forall
        fun B => ?_))
      show charFn ρ (A * x * (B⁻¹)⁻¹ * x⁻¹) * charFn ρ (B⁻¹ * x * A⁻¹ * x⁻¹)
          = charFn ρ (A * x * B * x⁻¹) * charFn ρ (B⁻¹ * x * A⁻¹ * x⁻¹)
      simp only [inv_inv]
    have hc : ∀ B : G, charFn ρ (B⁻¹ * x * A⁻¹ * x⁻¹)
        = charFn ρ ((x * A⁻¹ * x⁻¹) * B⁻¹ * 1) := by
      intro B
      have h1 : B⁻¹ * x * A⁻¹ * x⁻¹ = B⁻¹ * (x * A⁻¹ * x⁻¹) := by
        simp only [mul_assoc]
      rw [h1, charFn_mul_comm, mul_one]
    have hfin : charFn ρ (x⁻¹ * (A * x) * 1 * (x * A⁻¹ * x⁻¹))
        = charFn ρ (A * (x * x) * A⁻¹ * (x * x)⁻¹) := by
      have hw : x⁻¹ * (A * x) * 1 * (x * A⁻¹ * x⁻¹)
          = x⁻¹ * ((A * (x * x) * A⁻¹ * (x * x)⁻¹) * x) := by group
      have hw2 : (A * (x * x) * A⁻¹ * (x * x)⁻¹) * x * x⁻¹
          = A * (x * x) * A⁻¹ * (x * x)⁻¹ := by group
      rw [hw, charFn_mul_comm]
      exact congrArg (charFn ρ) hw2
    rw [hsub]
    calc ∫ B, charFn ρ (A * x * B * x⁻¹) * charFn ρ (B⁻¹ * x * A⁻¹ * x⁻¹) ∂μG
        = ∫ B, charFn ρ ((A * x) * B * x⁻¹)
            * charFn ρ ((x * A⁻¹ * x⁻¹) * B⁻¹ * 1) ∂μG :=
          integral_congr_ae (Filter.Eventually.of_forall fun B => by
            show charFn ρ (A * x * B * x⁻¹) * charFn ρ (B⁻¹ * x * A⁻¹ * x⁻¹)
                = charFn ρ ((A * x) * B * x⁻¹)
                  * charFn ρ ((x * A⁻¹ * x⁻¹) * B⁻¹ * 1)
            rw [hc B])
      _ = (d : ℂ)⁻¹ * charFn ρ (x⁻¹ * (A * x) * 1 * (x * A⁻¹ * x⁻¹)) :=
          integral_charFn_mul_charFn_inv ρ μG hρcont hρirr (A * x) (x⁻¹)
            (x * A⁻¹ * x⁻¹) 1
      _ = (d : ℂ)⁻¹ * charFn ρ (A * (x * x) * A⁻¹ * (x * x)⁻¹) := by
          rw [hfin]
  calc ∫ A, ∫ B, charFn ρ (A * x * B⁻¹ * x⁻¹) * charFn ρ (B * x * A⁻¹ * x⁻¹)
        ∂μG ∂μG
      = ∫ A, (d : ℂ)⁻¹ * charFn ρ (A * (x * x) * A⁻¹ * (x * x)⁻¹) ∂μG :=
        integral_congr_ae (Filter.Eventually.of_forall hinner)
    _ = (d : ℂ)⁻¹ * ∫ A, charFn ρ (A * (x * x) * A⁻¹ * (x * x)⁻¹) ∂μG :=
        integral_const_mul _ _
    _ = (d : ℂ)⁻¹ * ((d : ℂ)⁻¹ * (charFn ρ (x * x) * star (charFn ρ (x * x)))) := by
        rw [integral_charFn_conj_twirl ρ μG hρcont hρirr hd (x * x)]
    _ = ((d : ℂ)⁻¹) ^ 2 * (charFn ρ (x * x) * star (charFn ρ (x * x))) := by
        rw [pow_two]; ring

/-! ## §4. Assembly: the named surviving term

Under PARTIAL (see the header), the brief's sign theorem does not
land.  What lands instead: the exact identities below, pinning
`κ₄^dep` on the diagonal to the named functional of the §1 unfolded
contractions, and the factor-nonnegativity corollary — `κ₄^dep` on
the diagonal is nonnegative at general `(G, ρ)` (no irreducibility)
as soon as the named functional is.  No sign for the functional is
asserted anywhere in this module. -/

section Diagonal

variable (u : LayerLink N → G)

/-- **The surviving term, named.**  `Φ(u)` is the sum, over the
primitive quads, of the excess of `quadReMoment` on the diagonal
over the `e₁⁴` baseline — exactly the functional whose sign
`kappa4dep_sign_reduction` reduces the sign of `κ₄^dep (u, u)` to.
No sign is asserted for it. -/
noncomputable def phiFunctional : ℝ :=
  ∑ C ∈ primitiveQuads, (quadReMoment ρ μG C u u - (e1 ρ μG) ^ 4)

/-- Membership in `primitiveQuads` is primitivity. -/
theorem isPrimitiveQuad_of_mem_primitiveQuads {C : Finset (LayerColumn N)}
    (hC : C ∈ primitiveQuads) : IsPrimitiveQuad C := by
  rw [primitiveQuads, Finset.mem_filter] at hC
  exact ⟨hC.2.1, hC.2.2⟩

/-- **`κ₄^dep` on the diagonal is the named functional.**  With
`kappa4dep_sign_reduction`, `κ₄^dep (u, u) = d⁻⁴ · Φ(u)` exactly,
at general `(G, ρ)` — no irreducibility used, no sign asserted. -/
theorem kappa4dep_diag_eq_phi (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) :
    kappa4dep ρ μG u u = ((d : ℝ)⁻¹) ^ 4 * phiFunctional ρ μG u := by
  rw [kappa4dep_sign_reduction ρ μG hN hN3 hρcont u u]
  rfl

/-- **Stage one, assembled on the diagonal**: `Φ(u)` is the
explicit contraction sum of stage one, minus the `e₁⁴` baseline
per primitive quad.  The sign of `Φ` is the sign of the part of
this expansion whose site contractions are the `ρ ⊗ ρ` and higher
tensor twirls named in the header. -/
theorem phiFunctional_eq (hρcont : Continuous fun g : G => repMatrix ρ g) :
    phiFunctional ρ μG u
      = ∑ C ∈ primitiveQuads, (((2 : ℝ)⁻¹) ^ 4
          * (∑ t ∈ C.powerset, quadCharMoment ρ μG C t u u).re
        - (e1 ρ μG) ^ 4) := by
  show (∑ C ∈ primitiveQuads, (quadReMoment ρ μG C u u - (e1 ρ μG) ^ 4))
    = _
  refine Finset.sum_congr rfl fun C hC => ?_
  rw [quadReMoment_primitive_eq ρ μG hρcont
    (isPrimitiveQuad_of_mem_primitiveQuads hC) u u]

/-- **The factor in front of the surviving term is nonnegative.**
`κ₄^dep (u, u) ≥ 0` at general `(G, ρ)` as soon as the named
functional `Φ(u) ≥ 0`; the open content of the sign question is
exactly `Φ`, nothing else. -/
theorem kappa4dep_diag_nonneg_of_phi_nonneg (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hΦ : 0 ≤ phiFunctional ρ μG u) :
    0 ≤ kappa4dep ρ μG u u := by
  rw [kappa4dep_diag_eq_phi ρ μG u hN hN3 hρcont]
  exact mul_nonneg (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg d)) 4) hΦ

end Diagonal

end Telescope

end ThetLogos
